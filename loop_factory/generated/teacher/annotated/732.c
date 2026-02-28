int main1(int m,int n,int p,int q){
  int b, j, v, h, f, e, d, w;

  b=(q%37)+4;
  j=0;
  v=b;
  h=m;
  f=n;
  e=p;
  d=m;
  w=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == \at(n, Pre) + j * v;

  loop invariant v == \at(q, Pre) % 37 + 4;
  loop invariant j >= 0;
  loop invariant f == n + j * ((q % 37) + 4);
  loop invariant h == m + j * n + ((q % 37) + 4) * j * (j - 1) / 2;
  loop invariant v == ((q % 37) + 4);
  loop invariant m == \at(m,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant f == n + j*v;


  loop invariant v == (q % 37) + 4;
  loop assigns h, f, j;
*/
while (1) {
      h = h+f;
      f = f+v;
      j = j+1;
  }

}
