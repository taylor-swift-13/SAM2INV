int main1(int b,int q){
  int vb, c4, iody, z0, unf, r, j0;

  vb=b+15;
  c4=vb+7;
  iody=0;
  z0=(b%28)+10;
  unf=0;
  r=b;
  j0=4;

  while (z0>iody) {
      z0 = z0 - iody;
      unf = unf*2;
      j0 = (c4)+(j0);
      iody += 1;
      r = r + unf;
  }

  while (vb>=unf+1) {
      vb -= 2;
  }

}
