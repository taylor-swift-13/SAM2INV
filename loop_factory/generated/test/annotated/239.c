int main1(int k,int m){
  int l, i, v;

  l=13;
  i=0;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant 0 <= i <= l;
   loop invariant l == 13;
   loop invariant m == \at(m, Pre);
   loop invariant k == \at(k, Pre);
   loop invariant (i == 0) ==> (v == m);
   loop invariant i <= l;
   loop invariant i >= 0;
   loop invariant i > 0 ==> v >= 0;
   loop assigns i, v;
   loop variant l - i;
 */
while (i<l) {
      v = v*v;
      i = i+1;
  }

}