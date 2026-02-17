int main1(int a,int k,int n){
  int l, i, v, z, s;

  l=69;
  i=l;
  v=k;
  z=-4;
  s=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant i + v - k == 69;
   loop invariant 0 <= i <= 69;
   loop invariant a == \at(a, Pre);
   loop invariant k == \at(k, Pre);
   loop invariant n == \at(n, Pre);
   loop assigns i, v;
   loop variant i;
 */
while (i>0) {
      v = v+1;
      i = i-1;
  }

}