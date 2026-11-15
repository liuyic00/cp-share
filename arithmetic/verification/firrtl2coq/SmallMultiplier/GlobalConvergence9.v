From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
From SmallMultiplier Require Import Model GlobalStable GlobalWidths GlobalProgressTypes GlobalFieldSteps GlobalScalarSteps GlobalProgress.
Local Open Scope N_scope.
From SmallMultiplier Require Import GlobalTypeProgress.
Lemma global_rank_chunk_9 invalid snapshot final v level (prior:global_ranked v level snapshot) (sizes:global_leaf_sizes v)
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => (global_rank_at index <= S level)%coq_nat -> global_value_at index final = Some (global_target_at index v)) (List.seq 1800 200).
Proof.
 constructor.
 - intro enough. exact (global_progress_1800 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1801 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1802 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1803 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1804 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1805 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1806 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1807 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1808 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1809 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1810 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1811 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1812 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1813 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1814 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1815 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1816 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1817 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1818 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1819 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1820 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1821 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1822 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1823 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1824 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1825 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1826 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1827 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1828 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1829 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1830 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1831 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1832 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1833 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1834 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1835 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1836 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1837 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1838 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1839 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1840 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1841 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1842 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1843 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1844 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1845 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1846 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1847 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1848 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1849 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1850 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1851 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1852 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1853 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1854 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1855 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1856 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1857 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1858 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1859 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1860 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1861 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1862 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1863 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1864 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1865 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1866 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1867 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1868 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1869 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1870 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1871 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1872 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1873 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1874 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1875 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1876 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1877 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1878 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1879 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1880 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1881 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1882 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1883 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1884 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1885 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1886 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1887 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1888 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1889 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1890 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1891 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1892 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1893 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1894 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1895 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1896 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1897 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1898 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1899 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1900 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1901 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1902 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1903 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1904 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1905 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1906 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1907 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1908 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1909 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1910 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1911 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1912 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1913 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1914 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1915 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1916 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1917 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1918 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1919 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1920 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1921 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1922 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1923 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1924 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1925 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1926 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1927 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1928 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1929 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1930 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1931 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1932 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1933 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1934 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1935 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1936 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1937 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1938 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1939 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1940 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1941 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1942 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1943 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1944 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1945 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1946 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1947 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1948 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1949 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1950 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1951 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1952 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1953 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1954 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1955 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1956 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1957 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1958 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1959 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1960 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1961 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1962 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1963 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1964 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1965 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1966 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1967 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1968 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1969 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1970 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1971 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1972 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1973 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1974 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1975 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1976 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1977 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1978 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1979 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1980 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1981 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1982 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1983 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1984 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1985 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1986 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1987 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1988 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1989 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1990 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1991 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1992 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1993 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1994 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1995 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1996 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1997 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1998 invalid snapshot final v level prior types sizes enough ran).
 constructor.
 - intro enough. exact (global_progress_1999 invalid snapshot final v level prior types sizes enough ran).
 constructor.
Qed.
Lemma global_type_chunk_9 invalid snapshot final
 (types:global_port_types snapshot)
 (ran:circuit_value_iter_with_memory_policy invalid generated_modules generated_top snapshot false=Some final) :
 List.Forall (fun index => global_port_at index=true -> option_map type_of_val (global_value_at index final)=Some(Gtyp(global_type_at index))) (List.seq 1800 200).
Proof.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro excluded. discriminate excluded.
 constructor.
 - intro included. exact (global_type_progress_1804 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1805 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1806 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1807 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_1872 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1873 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1874 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1875 invalid snapshot final types ran).
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
 - intro included. exact (global_type_progress_1940 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1941 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1942 invalid snapshot final types ran).
 constructor.
 - intro included. exact (global_type_progress_1943 invalid snapshot final types ran).
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
