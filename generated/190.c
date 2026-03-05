int main190(int h,int x,int g){
  int dwm, aa, nbl, mi, cbd;

  dwm=x+8;
  aa=0;
  nbl=4;
  mi=-5;
  cbd=aa;

  while (aa<=dwm-1) {
      mi = mi + 3;
      aa += 1;
      nbl = nbl + 3;
      g += nbl;
      cbd = cbd+(nbl%2);
      x = x+(nbl%4);
  }

}
