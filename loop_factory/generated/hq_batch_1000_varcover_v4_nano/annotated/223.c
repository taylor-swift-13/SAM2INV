int main1(int k,int n,int q){
  int l, i, v, a, g, f, b;

  l=36;
  i=l;
  v=k;
  a=q;
  g=-5;
  f=i;
  b=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant i <= l;
   loop invariant i >= 0;
   loop invariant ((v - k) % 2 == 0);
   loop invariant k == \at(k,Pre);
   loop invariant n == \at(n,Pre);
   loop invariant q == \at(q,Pre);
   loop assigns i, v;
   loop variant i;
 */
while (i>0) {
      v = v*3+4;
      i = i-1;
  }

}