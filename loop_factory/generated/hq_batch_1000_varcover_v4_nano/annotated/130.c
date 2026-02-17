int main1(int b,int m,int n){
  int l, i, v;

  l=m;
  i=0;
  v=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant l == m;
   loop invariant i >= 0;
   loop invariant (l >= 0) ==> (i <= l);
   loop invariant (i == 0) ==> (v == b);
   loop assigns i, v;
   loop variant (l - i);
 */
while (i<l) {
      v = v-v;
      v = v+2;
      if (i+2<=v+l) {
          v = v+v;
      }
      i = i+1;
  }

}