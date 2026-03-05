int main59(int f,int a,int u){
  int oj, xt, nue, nrs, ipz, z;

  oj=0;
  xt=0;
  nue=0;
  nrs=(f%18)+5;
  ipz=8;
  z=a;

  while (nrs>0) {
      nue = nue+f*a;
      nrs--;
      ipz = ipz + 3;
      xt = xt+a*a;
      oj = oj+f*f;
      z = z*3+(nrs%3)+1;
  }

}
