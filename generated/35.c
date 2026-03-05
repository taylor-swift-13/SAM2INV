int main35(int a,int k){
  int u, cu, f7, q, r, t749;

  u=0;
  cu=(a%18)+5;
  f7=(a%15)+3;
  q=cu;
  r=u;
  t749=k;

  while (cu!=0) {
      f7 -= 1;
      cu--;
      q += 2;
      t749 = t749 + u;
      r = r+(cu%2);
      a = a+(f7%8);
  }

}
