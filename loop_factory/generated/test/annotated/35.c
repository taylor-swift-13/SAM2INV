int main1(int k,int m,int p,int q){
  int l, i, v, s;

  l=29;
  i=l;
  v=8;
  s=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant i >= 0;
   loop invariant i <= l;
   loop invariant v == 8 + (l - i) * 2 * s;
   loop invariant s == q;
   loop invariant l == 29;
   loop invariant v == 8 + 2*s*(29 - i);
   loop invariant s == \at(q, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && p == \at(p, Pre) && q == \at(q, Pre);
   loop invariant i <= 29;
   loop invariant k == \at(k, Pre);
   loop invariant m == \at(m, Pre);
   loop invariant p == \at(p, Pre);
   loop invariant q == \at(q, Pre);
   loop invariant v == 8 + 2*s*(l - i);
   loop invariant i >= 0 && i <= 29;
   loop invariant v + 2*s*i == 8 + 58*s;
   loop assigns i, v;
 */
while (i>0) {
      v = v+s+s;
      i = i-1;
  }

}