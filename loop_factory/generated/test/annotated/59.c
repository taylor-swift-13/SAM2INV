int main1(int k,int m,int n,int p){
  int l, i, v, a, r;

  l=51;
  i=l;
  v=p;
  a=k;
  r=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant k == \at(k, Pre) && p == \at(p, Pre) && m == \at(m, Pre) && n == \at(n, Pre);
   loop invariant (a - k) % r == 0;
   loop invariant v == p + ((a - k) / r) * k + r * ((a - k) / r) * (((a - k) / r) - 1) / 2;
   loop invariant i >= 0;
   loop invariant i <= 51;
   loop invariant a >= k;
   loop invariant k == \at(k, Pre);
   loop invariant m == \at(m, Pre);
   loop invariant n == \at(n, Pre);
   loop invariant p == \at(p, Pre);
   loop invariant l == 51;
   loop invariant v == p + ((a - k)/r)*k + r * ((a - k)/r) * (((a - k)/r) - 1) / 2;
   loop invariant r == l;
   loop invariant i <= l;
   loop invariant k == \at(k,Pre);
   loop invariant m == \at(m,Pre);
   loop invariant p == \at(p,Pre);
   loop invariant (a - k) % 51 == 0;
   loop assigns v, a, i;
 */
while (i>0) {
      v = v+a;
      a = a+r;
      i = i/2;
  }

}