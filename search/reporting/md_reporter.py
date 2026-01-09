"""
Markdown Reporter - Generates human-readable reports from execution results.

Converts JSONL logs and execution summaries into formatted Markdown documents
for easy review and documentation of research runs.
"""

import json
import time
from pathlib import Path
from typing import Any, Dict, List, Optional


class MarkdownReporter:
    """
    Generates Markdown reports from agent execution results.
    
    Reports include:
    - Execution summary (run ID, duration, status)
    - Agent results table
    - Configuration details
    - Artifacts generated
    - Links to JSONL logs
    """
    
    def __init__(self, output_dir: Optional[Path] = None):
        """
        Initialize reporter with output directory.
        
        Args:
            output_dir: Directory to save reports (default: docs/reports/)
        """
        if output_dir is None:
            # Use repo root / docs / reports
            repo_root = Path(__file__).parent.parent.parent
            output_dir = repo_root / "docs" / "reports"
        
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        print(f"[REPORTER] Output directory: {self.output_dir}")
    
    def generate_report(
        self,
        summary: Dict[str, Any],
        log_file: Optional[Path] = None,
    ) -> Path:
        """
        Generate Markdown report from execution summary.
        
        Args:
            summary: Execution summary dictionary from Supervisor
            log_file: Optional path to JSONL log file
        
        Returns:
            Path to generated Markdown report
        """
        print(f"[REPORTER] Generating report for run {summary.get('run_id', 'unknown')}")
        
        # Generate filename with timestamp
        timestamp = time.strftime("%Y-%m-%d_%H-%M-%S")
        run_id = summary.get("run_id", "unknown")
        filename = f"{timestamp}_{run_id}.md"
        report_path = self.output_dir / filename
        
        # Build report content
        content = self._build_report_content(summary, log_file)
        
        # Write to file
        with open(report_path, "w") as f:
            f.write(content)
        
        print(f"[REPORTER] Report saved: {report_path}")
        return report_path
    
    def _build_report_content(
        self,
        summary: Dict[str, Any],
        log_file: Optional[Path] = None,
    ) -> str:
        """
        Build Markdown content from summary.
        
        Args:
            summary: Execution summary
            log_file: Optional log file path
        
        Returns:
            Markdown content string
        """
        lines = []
        
        # Header
        lines.append(f"# SATurday Research Run Report")
        lines.append("")
        lines.append(f"**Generated:** {time.strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append(f"**Run ID:** `{summary.get('run_id', 'unknown')}`")
        lines.append("")
        
        # Executive Summary
        lines.append("## Executive Summary")
        lines.append("")
        
        total_time = summary.get("total_time_seconds", 0)
        lines.append(f"- **Total Duration:** {total_time:.3f} seconds")
        lines.append(f"- **Random Seed:** {summary.get('seed', 'unknown')}")
        
        # Count agent statuses
        agents = summary.get("agents", {})
        success_count = sum(1 for a in agents.values() if a.get("status") == "success")
        failure_count = sum(1 for a in agents.values() if a.get("status") == "failure")
        
        lines.append(f"- **Agents Executed:** {len(agents)}")
        lines.append(f"- **Successful:** {success_count}")
        lines.append(f"- **Failed:** {failure_count}")
        lines.append("")
        
        # Agent Results
        lines.append("## Agent Results")
        lines.append("")
        
        if agents:
            lines.append("| Agent | Status | Duration (s) | Metrics |")
            lines.append("|-------|--------|--------------|---------|")
            
            for agent_name, agent_data in agents.items():
                status = agent_data.get("status", "unknown")
                duration = agent_data.get("duration", 0)
                metrics = agent_data.get("metrics", {})
                
                # Format status with indicator
                status_icon = "✓" if status == "success" else "✗" if status == "failure" else "?"
                status_text = f"{status_icon} {status}"
                
                # Format metrics
                metrics_text = ", ".join(f"{k}={v}" for k, v in metrics.items()) if metrics else "-"
                if len(metrics_text) > 40:
                    metrics_text = metrics_text[:37] + "..."
                
                lines.append(f"| {agent_name} | {status_text} | {duration:.3f} | {metrics_text} |")
            
            lines.append("")
        else:
            lines.append("No agents executed.")
            lines.append("")
        
        # Configuration Details
        lines.append("## Configuration")
        lines.append("")
        lines.append("Configuration used for this run:")
        lines.append("")
        lines.append("```yaml")
        
        # Extract key config fields
        config_highlights = {
            "seed": summary.get("seed", 42),
            "run_id": summary.get("run_id", "unknown"),
            "total_time": f"{total_time:.3f}s",
        }
        
        for key, value in config_highlights.items():
            lines.append(f"{key}: {value}")
        
        lines.append("```")
        lines.append("")
        
        # Artifacts Section
        lines.append("## Artifacts Generated")
        lines.append("")
        
        # Check if agents produced artifacts
        has_artifacts = False
        for agent_name, agent_data in agents.items():
            # Look for artifact info in metrics or status
            if agent_data.get("metrics"):
                has_artifacts = True
                break
        
        if has_artifacts:
            lines.append("Artifacts generated during this run:")
            lines.append("")
            
            for agent_name, agent_data in agents.items():
                metrics = agent_data.get("metrics", {})
                if metrics:
                    lines.append(f"### {agent_name}")
                    lines.append("")
                    for key, value in metrics.items():
                        lines.append(f"- **{key}:** {value}")
                    lines.append("")
        else:
            lines.append("No artifacts were generated during this run.")
            lines.append("")
        
        # Logs Reference
        lines.append("## Logs and Data")
        lines.append("")
        
        if log_file:
            lines.append(f"- **JSONL Log:** `{log_file}`")
        elif "log_file" in summary:
            lines.append(f"- **JSONL Log:** `{summary['log_file']}`")
        else:
            lines.append("- **JSONL Log:** Not available")
        
        lines.append("")
        
        # Acceptance Criteria
        lines.append("## Acceptance Criteria")
        lines.append("")
        
        all_success = all(a.get("status") == "success" for a in agents.values())
        
        if all_success:
            lines.append("- All agents completed successfully")
            lines.append("- No errors detected")
            lines.append("- **Status:** PASS")
        else:
            lines.append("- Some agents failed")
            lines.append("- Review errors in JSONL log")
            lines.append("- **Status:** FAIL")
        
        lines.append("")
        
        # Next Steps
        lines.append("## Next Steps")
        lines.append("")
        
        if all_success:
            lines.append("- Review generated artifacts")
            lines.append("- Verify proofs with `satday check-proofs`")
            lines.append("- Run Lean verification with `satday verify`")
            lines.append("- Examine JSONL logs for detailed execution trace")
        else:
            lines.append("- Review error messages in JSONL log")
            lines.append("- Check agent-specific logs for failure details")
            lines.append("- Adjust configuration and retry")
        
        lines.append("")
        
        # Footer
        lines.append("---")
        lines.append("")
        lines.append("*Generated by SATurday Markdown Reporter*")
        lines.append("")
        
        return "\n".join(lines)
    
    def generate_from_jsonl(self, log_file: Path) -> Path:
        """
        Generate report by parsing JSONL log file.
        
        Args:
            log_file: Path to JSONL log file
        
        Returns:
            Path to generated report
        """
        print(f"[REPORTER] Parsing JSONL log: {log_file}")
        
        # Parse JSONL to extract summary
        events = []
        with open(log_file, "r") as f:
            for line in f:
                if line.strip():
                    events.append(json.loads(line))
        
        # Extract key information
        run_id = events[0].get("run_id", "unknown") if events else "unknown"
        seed = events[0].get("seed", 42) if events else 42
        
        # Find pipeline start and complete events
        start_event = next((e for e in events if e.get("event") == "pipeline_start"), {})
        complete_event = next((e for e in events if e.get("event") == "pipeline_complete"), {})
        
        # Extract agent results
        agent_events = [e for e in events if e.get("event") == "agent_complete"]
        agents = {}
        
        for event in agent_events:
            agent_name = event.get("agent", "unknown")
            result = event.get("result", {})
            agents[agent_name] = {
                "status": result.get("status", "unknown"),
                "duration": result.get("duration_seconds", 0),
                "metrics": result.get("metrics", {}),
            }
        
        # Build summary
        summary = {
            "run_id": run_id,
            "seed": seed,
            "total_time_seconds": complete_event.get("total_time_seconds", 0),
            "agents": agents,
            "log_file": str(log_file),
        }
        
        return self.generate_report(summary, log_file=log_file)
    
    def generate_batch_summary(self, log_files: List[Path]) -> Path:
        """
        Generate summary report for multiple runs.
        
        Args:
            log_files: List of JSONL log files
        
        Returns:
            Path to summary report
        """
        print(f"[REPORTER] Generating batch summary for {len(log_files)} runs")
        
        # Generate filename
        timestamp = time.strftime("%Y-%m-%d_%H-%M-%S")
        filename = f"batch_summary_{timestamp}.md"
        report_path = self.output_dir / filename
        
        lines = []
        
        # Header
        lines.append("# SATurday Batch Run Summary")
        lines.append("")
        lines.append(f"**Generated:** {time.strftime('%Y-%m-%d %H:%M:%S')}")
        lines.append(f"**Total Runs:** {len(log_files)}")
        lines.append("")
        
        # Summary table
        lines.append("## Run Summary")
        lines.append("")
        lines.append("| Run ID | Duration (s) | Agents | Status |")
        lines.append("|--------|--------------|--------|--------|")
        
        for log_file in log_files:
            # Parse each log
            try:
                with open(log_file, "r") as f:
                    events = [json.loads(line) for line in f if line.strip()]
                
                run_id = events[0].get("run_id", "unknown")[:8] if events else "unknown"
                complete = next((e for e in events if e.get("event") == "pipeline_complete"), {})
                duration = complete.get("total_time_seconds", 0)
                num_agents = complete.get("num_agents", 0)
                
                # Check for failures
                agent_events = [e for e in events if e.get("event") == "agent_complete"]
                has_failure = any(
                    e.get("result", {}).get("status") == "failure"
                    for e in agent_events
                )
                
                status = "✗ FAIL" if has_failure else "✓ PASS"
                
                lines.append(f"| {run_id} | {duration:.3f} | {num_agents} | {status} |")
            
            except Exception as e:
                print(f"[REPORTER] Warning: Failed to parse {log_file}: {e}")
                lines.append(f"| ERROR | - | - | Parse failed |")
        
        lines.append("")
        
        # Footer
        lines.append("---")
        lines.append("")
        lines.append("*Generated by SATurday Markdown Reporter*")
        lines.append("")
        
        content = "\n".join(lines)
        
        with open(report_path, "w") as f:
            f.write(content)
        
        print(f"[REPORTER] Batch summary saved: {report_path}")
        return report_path

