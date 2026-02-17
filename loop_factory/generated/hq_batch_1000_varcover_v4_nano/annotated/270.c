int main1(int a,int k,int p,int q){
  int l, i, v, h, z, m, o, r, c, u;

  l=51;
  i=0;
  v=q;
  h=i;
  z=5;
  m=-1;
  o=k;
  r=6;
  c=q;
  u=i;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant (i == 0) ==> (h == 0);

    loop invariant (i == 0) ==> (v == q);

    loop invariant l == 51;

    loop assigns v, h, i;

  */
  while (i<l) {
      v = v*2+4;
      h = h*v+4;
      h = h*h+v;
      i = i+1;
  }

}