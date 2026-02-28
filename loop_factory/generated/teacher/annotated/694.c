int main1(int a,int m,int p,int q){
  int s, j, w, v, g;

  s=q+6;
  j=0;
  w=p;
  v=-2;
  g=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (v == 2*w) || (w == p && v == -2);
  loop invariant w >= p;

  loop invariant s == q + 6;
  loop invariant ((v == 2*w) || (v == -2 && w == p));
  loop invariant w >= \at(p, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant (v == 2*w) || (v == -2 && w == \at(p, Pre));
  loop invariant s == \at(q, Pre) + 6;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop assigns v, w;
*/
while (1) {
      v = w;
      w = w+1;
      v = v+w;
      v = v+1;
  }

}
