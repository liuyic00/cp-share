import Proofs.WhitelistFullWidth
namespace NutShellProofs
open nNutCore
namespace whitelistEncoding
def v30883 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 19
def v30885 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30886 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30885 instr))
def v30887 (instr : BitVec 32) : BitVec 1 := if (v30883 instr) = (v30886 instr) then 1 else 0
def v30888 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8211
def v30889 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30890 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30889 instr))
def v30891 (instr : BitVec 32) : BitVec 1 := if (v30888 instr) = (v30890 instr) then 1 else 0
def v30892 (instr : BitVec 32) : BitVec 1 := ((v30887 instr) ||| (v30891 instr))
def v30893 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 12307
def v30894 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30895 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30894 instr))
def v30896 (instr : BitVec 32) : BitVec 1 := if (v30893 instr) = (v30895 instr) then 1 else 0
def v30897 (instr : BitVec 32) : BitVec 1 := ((v30892 instr) ||| (v30896 instr))
def v30898 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28691
def v30899 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30900 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30899 instr))
def v30901 (instr : BitVec 32) : BitVec 1 := if (v30898 instr) = (v30900 instr) then 1 else 0
def v30902 (instr : BitVec 32) : BitVec 1 := ((v30897 instr) ||| (v30901 instr))
def v30903 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24595
def v30904 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30905 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30904 instr))
def v30906 (instr : BitVec 32) : BitVec 1 := if (v30903 instr) = (v30905 instr) then 1 else 0
def v30907 (instr : BitVec 32) : BitVec 1 := ((v30902 instr) ||| (v30906 instr))
def v30908 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16403
def v30909 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30910 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30909 instr))
def v30911 (instr : BitVec 32) : BitVec 1 := if (v30908 instr) = (v30910 instr) then 1 else 0
def v30912 (instr : BitVec 32) : BitVec 1 := ((v30907 instr) ||| (v30911 instr))
def v30913 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4115
def v14809 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4227887231
def v30914 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14809 instr))
def v30915 (instr : BitVec 32) : BitVec 1 := if (v30913 instr) = (v30914 instr) then 1 else 0
def v30916 (instr : BitVec 32) : BitVec 1 := ((v30912 instr) ||| (v30915 instr))
def v30917 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20499
def v30918 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14809 instr))
def v30919 (instr : BitVec 32) : BitVec 1 := if (v30917 instr) = (v30918 instr) then 1 else 0
def v30920 (instr : BitVec 32) : BitVec 1 := ((v30916 instr) ||| (v30919 instr))
def v30921 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1073762323
def v30922 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14809 instr))
def v30923 (instr : BitVec 32) : BitVec 1 := if (v30921 instr) = (v30922 instr) then 1 else 0
def v30924 (instr : BitVec 32) : BitVec 1 := ((v30920 instr) ||| (v30923 instr))
def v30925 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 55
def v30926 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 127
def v30927 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30926 instr))
def v30928 (instr : BitVec 32) : BitVec 1 := if (v30925 instr) = (v30927 instr) then 1 else 0
def v30929 (instr : BitVec 32) : BitVec 1 := ((v30924 instr) ||| (v30928 instr))
def v30930 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 23
def v30931 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 127
def v30932 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30931 instr))
def v30933 (instr : BitVec 32) : BitVec 1 := if (v30930 instr) = (v30932 instr) then 1 else 0
def v30934 (instr : BitVec 32) : BitVec 1 := ((v30929 instr) ||| (v30933 instr))
def v30935 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 27
def v30936 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30937 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30936 instr))
def v30938 (instr : BitVec 32) : BitVec 1 := if (v30935 instr) = (v30937 instr) then 1 else 0
def v30939 (instr : BitVec 32) : BitVec 1 := ((v30934 instr) ||| (v30938 instr))
def v30940 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4123
def v14576 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4261441663
def v30941 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v30942 (instr : BitVec 32) : BitVec 1 := if (v30940 instr) = (v30941 instr) then 1 else 0
def v30943 (instr : BitVec 32) : BitVec 1 := ((v30939 instr) ||| (v30942 instr))
def v30944 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20507
def v30945 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v30946 (instr : BitVec 32) : BitVec 1 := if (v30944 instr) = (v30945 instr) then 1 else 0
def v30947 (instr : BitVec 32) : BitVec 1 := ((v30943 instr) ||| (v30946 instr))
def v30948 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20507
def v30949 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v30950 (instr : BitVec 32) : BitVec 1 := if (v30948 instr) = (v30949 instr) then 1 else 0
def v30951 (instr : BitVec 32) : BitVec 1 := ((v30947 instr) ||| (v30950 instr))
def v30952 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1073762331
def v30953 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v30954 (instr : BitVec 32) : BitVec 1 := if (v30952 instr) = (v30953 instr) then 1 else 0
def v30955 (instr : BitVec 32) : BitVec 1 := ((v30951 instr) ||| (v30954 instr))
def v30956 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 3
def v30957 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30958 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30957 instr))
def v30959 (instr : BitVec 32) : BitVec 1 := if (v30956 instr) = (v30958 instr) then 1 else 0
def v30960 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4099
def v30961 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30962 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30961 instr))
def v30963 (instr : BitVec 32) : BitVec 1 := if (v30960 instr) = (v30962 instr) then 1 else 0
def v30964 (instr : BitVec 32) : BitVec 1 := ((v30959 instr) ||| (v30963 instr))
def v30965 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8195
def v30966 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30967 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30966 instr))
def v30968 (instr : BitVec 32) : BitVec 1 := if (v30965 instr) = (v30967 instr) then 1 else 0
def v30969 (instr : BitVec 32) : BitVec 1 := ((v30964 instr) ||| (v30968 instr))
def v30970 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16387
def v30971 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30972 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30971 instr))
def v30973 (instr : BitVec 32) : BitVec 1 := if (v30970 instr) = (v30972 instr) then 1 else 0
def v30974 (instr : BitVec 32) : BitVec 1 := ((v30969 instr) ||| (v30973 instr))
def v30975 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20483
def v30976 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30977 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30976 instr))
def v30978 (instr : BitVec 32) : BitVec 1 := if (v30975 instr) = (v30977 instr) then 1 else 0
def v30979 (instr : BitVec 32) : BitVec 1 := ((v30974 instr) ||| (v30978 instr))
def v30980 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 35
def v30981 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30982 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30981 instr))
def v30983 (instr : BitVec 32) : BitVec 1 := if (v30980 instr) = (v30982 instr) then 1 else 0
def v30984 (instr : BitVec 32) : BitVec 1 := ((v30979 instr) ||| (v30983 instr))
def v30985 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4131
def v30986 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30987 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30986 instr))
def v30988 (instr : BitVec 32) : BitVec 1 := if (v30985 instr) = (v30987 instr) then 1 else 0
def v30989 (instr : BitVec 32) : BitVec 1 := ((v30984 instr) ||| (v30988 instr))
def v30990 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8227
def v30991 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30992 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30991 instr))
def v30993 (instr : BitVec 32) : BitVec 1 := if (v30990 instr) = (v30992 instr) then 1 else 0
def v30994 (instr : BitVec 32) : BitVec 1 := ((v30989 instr) ||| (v30993 instr))
def v30995 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24579
def v30996 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v30997 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v30996 instr))
def v30998 (instr : BitVec 32) : BitVec 1 := if (v30995 instr) = (v30997 instr) then 1 else 0
def v30999 (instr : BitVec 32) : BitVec 1 := ((v30994 instr) ||| (v30998 instr))
def v31000 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 12291
def v31001 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v31002 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v31001 instr))
def v31003 (instr : BitVec 32) : BitVec 1 := if (v31000 instr) = (v31002 instr) then 1 else 0
def v31004 (instr : BitVec 32) : BitVec 1 := ((v30999 instr) ||| (v31003 instr))
def v31005 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 12323
def v31006 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v31007 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v31006 instr))
def v31008 (instr : BitVec 32) : BitVec 1 := if (v31005 instr) = (v31007 instr) then 1 else 0
def v31009 (instr : BitVec 32) : BitVec 1 := ((v31004 instr) ||| (v31008 instr))
def v31010 (instr : BitVec 32) : BitVec 1 := ((v30955 instr) ||| (v31009 instr))
def v31011 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 51
def v31012 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v31013 (instr : BitVec 32) : BitVec 1 := if (v31011 instr) = (v31012 instr) then 1 else 0
def v31014 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 8243
def v31015 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v31016 (instr : BitVec 32) : BitVec 1 := if (v31014 instr) = (v31015 instr) then 1 else 0
def v31017 (instr : BitVec 32) : BitVec 1 := ((v31013 instr) ||| (v31016 instr))
def v31018 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 12339
def v31019 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v31020 (instr : BitVec 32) : BitVec 1 := if (v31018 instr) = (v31019 instr) then 1 else 0
def v31021 (instr : BitVec 32) : BitVec 1 := ((v31017 instr) ||| (v31020 instr))
def v31022 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28723
def v31023 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v31024 (instr : BitVec 32) : BitVec 1 := if (v31022 instr) = (v31023 instr) then 1 else 0
def v31025 (instr : BitVec 32) : BitVec 1 := ((v31021 instr) ||| (v31024 instr))
def v31026 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24627
def v31027 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v31028 (instr : BitVec 32) : BitVec 1 := if (v31026 instr) = (v31027 instr) then 1 else 0
def v31029 (instr : BitVec 32) : BitVec 1 := ((v31025 instr) ||| (v31028 instr))
def v31030 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16435
def v31031 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v31032 (instr : BitVec 32) : BitVec 1 := if (v31030 instr) = (v31031 instr) then 1 else 0
def v31033 (instr : BitVec 32) : BitVec 1 := ((v31029 instr) ||| (v31032 instr))
def v31034 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4147
def v31035 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v31036 (instr : BitVec 32) : BitVec 1 := if (v31034 instr) = (v31035 instr) then 1 else 0
def v31037 (instr : BitVec 32) : BitVec 1 := ((v31033 instr) ||| (v31036 instr))
def v31038 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20531
def v31039 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v31040 (instr : BitVec 32) : BitVec 1 := if (v31038 instr) = (v31039 instr) then 1 else 0
def v31041 (instr : BitVec 32) : BitVec 1 := ((v31037 instr) ||| (v31040 instr))
def v31042 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1073741875
def v31043 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v31044 (instr : BitVec 32) : BitVec 1 := if (v31042 instr) = (v31043 instr) then 1 else 0
def v31045 (instr : BitVec 32) : BitVec 1 := ((v31041 instr) ||| (v31044 instr))
def v31046 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 1073762355
def v31047 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v14576 instr))
def v31048 (instr : BitVec 32) : BitVec 1 := if (v31046 instr) = (v31047 instr) then 1 else 0
def v31049 (instr : BitVec 32) : BitVec 1 := ((v31045 instr) ||| (v31048 instr))
def v31050 (instr : BitVec 32) : BitVec 1 := ((v31010 instr) ||| (v31049 instr))
def v31051 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 111
def v31052 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 127
def v31053 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v31052 instr))
def v31054 (instr : BitVec 32) : BitVec 1 := if (v31051 instr) = (v31053 instr) then 1 else 0
def v31055 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 103
def v31056 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v31057 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v31056 instr))
def v31058 (instr : BitVec 32) : BitVec 1 := if (v31055 instr) = (v31057 instr) then 1 else 0
def v31059 (instr : BitVec 32) : BitVec 1 := ((v31054 instr) ||| (v31058 instr))
def v31060 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 99
def v31061 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v31062 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v31061 instr))
def v31063 (instr : BitVec 32) : BitVec 1 := if (v31060 instr) = (v31062 instr) then 1 else 0
def v31064 (instr : BitVec 32) : BitVec 1 := ((v31059 instr) ||| (v31063 instr))
def v31065 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 4195
def v31066 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v31067 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v31066 instr))
def v31068 (instr : BitVec 32) : BitVec 1 := if (v31065 instr) = (v31067 instr) then 1 else 0
def v31069 (instr : BitVec 32) : BitVec 1 := ((v31064 instr) ||| (v31068 instr))
def v31070 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 16483
def v31071 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v31072 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v31071 instr))
def v31073 (instr : BitVec 32) : BitVec 1 := if (v31070 instr) = (v31072 instr) then 1 else 0
def v31074 (instr : BitVec 32) : BitVec 1 := ((v31069 instr) ||| (v31073 instr))
def v31075 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 24675
def v31076 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v31077 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v31076 instr))
def v31078 (instr : BitVec 32) : BitVec 1 := if (v31075 instr) = (v31077 instr) then 1 else 0
def v31079 (instr : BitVec 32) : BitVec 1 := ((v31074 instr) ||| (v31078 instr))
def v31080 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 20579
def v31081 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v31082 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v31081 instr))
def v31083 (instr : BitVec 32) : BitVec 1 := if (v31080 instr) = (v31082 instr) then 1 else 0
def v31084 (instr : BitVec 32) : BitVec 1 := ((v31079 instr) ||| (v31083 instr))
def v31085 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28771
def v31086 (instr : BitVec 32) : BitVec 32 := BitVec.ofNat 32 28799
def v31087 (instr : BitVec 32) : BitVec 32 := ((instr) &&& (v31086 instr))
def v31088 (instr : BitVec 32) : BitVec 1 := if (v31085 instr) = (v31087 instr) then 1 else 0
def v31089 (instr : BitVec 32) : BitVec 1 := ((v31084 instr) ||| (v31088 instr))
def v31090 (instr : BitVec 32) : BitVec 1 := ((v31050 instr) ||| (v31089 instr))
end whitelistEncoding

def AllowedInstruction (instr : BitVec 64) : Prop :=
  whitelistEncoding.v31090 (BitVec.extractLsb' 0 32 instr) = 1

theorem actual_whitelist_encoding (s : State) (i : Inputs) :
    v31090 s i = whitelistEncoding.v31090 (v30884 s i) := by rfl

theorem original_assumptions_allowed_instruction (s : State) (i : Inputs)
    (environment : assumes s i) (reset : i.g0.nreset = 0)
    (valid : v10100 s i = 1) : AllowedInstruction (v11105 s i) := by
  have all : (assumptionChecks0 s i).all id = true := environment
  simp only [assumptionChecks0, List.all_cons, List.all_nil, Bool.and_eq_true,
    Bool.true_and, Bool.and_true] at all
  have check : v31092 s i ≠ 1 ∨ v31090 s i = 1 := of_decide_eq_true all.1
  have gate : v31092 s i = 1 := by
    simp [v31092, v31091, v0, v24, reset, valid]
  have allowed := check.resolve_left (not_not_intro gate)
  rw [actual_whitelist_encoding] at allowed
  exact allowed

#print axioms original_assumptions_allowed_instruction
end NutShellProofs
