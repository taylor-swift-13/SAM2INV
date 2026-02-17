int main1(int k,int m,int n,int p){
  int l, i, v, h, x, z, t, c;

  l=n+19;
  i=0;
  v=p;
  h=p;
  x=n;
  z=p;
  t=8;
  c=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant 0 <= i;
   loop invariant (l >= 0) ==> (i <= l);
   loop invariant (i == 0) ==> (v == p);
   loop invariant (i > 0) ==> (v % 3 == 0);
   loop invariant (i == 0) ==> (h == p);
   loop invariant (i == 0) ==> (c == m);
   loop assigns v, h, c, i;
 */
while (i<l) {
      v = v*3+3;
      h = h*v+3;
      c = c*c+z;
      i = i+1;
  }

}