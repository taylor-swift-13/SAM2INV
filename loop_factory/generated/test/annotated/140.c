int main1(int k,int n,int p,int q){
  int l, i, v;

  l=63;
  i=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@

   loop invariant i % 2 == 0;
   loop invariant l == 63;
   loop invariant k == \at(k, Pre);
   loop invariant p == \at(p, Pre);
   loop invariant q == \at(q, Pre);
   loop invariant 0 <= i;
   loop invariant p == \at(p, Pre) && k == \at(k, Pre) && n == \at(n, Pre) && q == \at(q, Pre);
   loop invariant (i == 0) ==> (v == p);
   loop invariant n == \at(n, Pre);
   loop invariant i <= l + 1;
   loop invariant (i != 0) ==> (v % 2 == 0);
   loop invariant (i % 2) == 0;
   loop invariant (i > 0) ==> (v % 2 == 0);
   loop assigns i, v;
 */
while (i<l) {
      if ((i%7)==0) {
          v = v+i;
      }
      else {
          v = v+1;
      }
      v = v+v;
      i = i+2;
  }

}