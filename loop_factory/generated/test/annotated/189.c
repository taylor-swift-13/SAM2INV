int main1(int k,int n,int p,int q){
  int l, i, v, h, g;

  l=35;
  i=0;
  v=0;
  h=-6;
  g=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant h == i - 6;
   loop invariant v == i * (g + i - 6);
   loop invariant i <= l;
   loop invariant i >= 0;
   loop invariant l == 35;
   loop invariant k == \at(k,Pre);
   loop invariant n == \at(n,Pre);
   loop invariant p == \at(p,Pre);
   loop invariant q == \at(q,Pre);
   loop invariant h == -6 + i;
   loop invariant g == p;
   loop invariant k == \at(k, Pre);
   loop invariant n == \at(n, Pre);
   loop invariant p == \at(p, Pre);
   loop invariant q == \at(q, Pre);
   loop invariant v == i*i + i*(p - 6);
   loop invariant v == (h + 6) * (g + h);
   loop assigns v, h, i;
 */
while (i<l) {
      v = v+h+g;
      v = v+1;
      h = h+1;
      v = v+i;
      i = i+1;
  }

}