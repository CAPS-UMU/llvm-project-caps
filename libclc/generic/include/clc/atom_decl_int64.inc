#define __CLC_DECLARE_ATOM(ADDRSPACE, TYPE) \
	_CLC_OVERLOAD _CLC_DECL TYPE __CLC_FUNCTION (volatile ADDRSPACE TYPE *, TYPE);

__CLC_DECLARE_ATOM(local, long)
__CLC_DECLARE_ATOM(local, ulong)
__CLC_DECLARE_ATOM(global, long)
__CLC_DECLARE_ATOM(global, ulong)

#undef __CLC_DECLARE_ATOM

#undef __CLC_FUNCTION