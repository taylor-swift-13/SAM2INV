int main1(int b,int n,int q){
  int l, i, v;

  l=58;
  i=0;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant l == 58;
   loop invariant 0 <= i && i <= l;
   loop invariant (i == 0) ==> (v == l);
   loop invariant (i > 0) ==> (v == 0);
   loop assigns i, v;
   loop variant l - i;
 */
while (i<l) {
      v = v-v;
      if (i+6<=q+l) {
          v = v+1;
      }
      v = v-v;
      v = v+v;
      i = i+1;
  }

}