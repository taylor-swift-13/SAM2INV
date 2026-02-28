int main1(int a,int m,int p){
  int g, x, f, v, k, i;

  g=m;
  x=1;
  f=0;
  v=p;
  k=m;
  i=x;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == f + 1;
  loop invariant g == m;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (i - f) == 1;
  loop invariant g == \at(m, Pre);
  loop invariant ((f == 0) && (v == p)) || (v + f == g);
  loop invariant i >= 1;
  loop invariant f >= 0;
  loop assigns v, f, i;
*/
while (1) {
      v = g-f;
      f = f+1;
      v = v-1;
      i = i+1;
  }

}
