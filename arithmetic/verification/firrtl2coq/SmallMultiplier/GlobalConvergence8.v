From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalTypeProgress.
Lemma global_rank_chunk_8 invalid snapshot final v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => (global_rank_at index <= S level)%coq_nat -> global_value_at index final = Some (global_target_at index v)) (List.seq 1600 200).
Proof.
 constructor.
 - intro enough. exact (global_progress_1600 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1601 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1602 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1603 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1604 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1605 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1606 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1607 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1608 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1609 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1610 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1611 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1612 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1613 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1614 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1615 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1616 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1617 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1618 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1619 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1620 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1621 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1622 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1623 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1624 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1625 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1626 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1627 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1628 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1629 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1630 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1631 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1632 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1633 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1634 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1635 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1636 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1637 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1638 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1639 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1640 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1641 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1642 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1643 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1644 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1645 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1646 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1647 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1648 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1649 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1650 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1651 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1652 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1653 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1654 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1655 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1656 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1657 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1658 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1659 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1660 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1661 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1662 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1663 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1664 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1665 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1666 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1667 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1668 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1669 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1670 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1671 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1672 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1673 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1674 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1675 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1676 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1677 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1678 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1679 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1680 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1681 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1682 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1683 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1684 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1685 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1686 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1687 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1688 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1689 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1690 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1691 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1692 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1693 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1694 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1695 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1696 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1697 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1698 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1699 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1700 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1701 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1702 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1703 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1704 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1705 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1706 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1707 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1708 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1709 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1710 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1711 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1712 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1713 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1714 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1715 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1716 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1717 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1718 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1719 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1720 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1721 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1722 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1723 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1724 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1725 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1726 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1727 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1728 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1729 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1730 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1731 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1732 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1733 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1734 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1735 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1736 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1737 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1738 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1739 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1740 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1741 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1742 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1743 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1744 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1745 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1746 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1747 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1748 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1749 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1750 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1751 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1752 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1753 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1754 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1755 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1756 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1757 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1758 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1759 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1760 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1761 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1762 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1763 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1764 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1765 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1766 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1767 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1768 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1769 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1770 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1771 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1772 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1773 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1774 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1775 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1776 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1777 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1778 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1779 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1780 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1781 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1782 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1783 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1784 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1785 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1786 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1787 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1788 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1789 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1790 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1791 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1792 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1793 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1794 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1795 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1796 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1797 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1798 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1799 invalid snapshot final v level prior types sizes enough ran).
 constructor.
Qed.
Lemma global_type_chunk_8 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => global_port_at index=true -> option_map type_of_val (global_value_at index final)=Some(Gtyp(global_type_at index))) (List.seq 1600 200).
Proof.
 constructor.
 - intro included. exact (global_type_progress_1600 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1601 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1602 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1603 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1668 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1669 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1670 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1671 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1736 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1737 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1738 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1739 invalid snapshot final types ran).
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
Qed.
