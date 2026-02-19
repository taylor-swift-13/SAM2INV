int main1(int b,int n){
  int l, i, v;

  l=74;
  i=0;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant (i == 0) ==> (v == 2);
   loop invariant (i != 0) ==> (v == i - 2);
   loop invariant i % 2 == 0;
   loop invariant i <= l;
   loop invariant b == \at(b, Pre);
   loop invariant n == \at(n, Pre);
   loop invariant l == 74;
   loop invariant i >= 0;
   loop invariant (i == 0 && v == 2) || (i > 0 && v == i - 2);
   loop invariant (i == 0 ==> v == 2) && (i > 0 ==> v == i - 2);
   loop invariant (i == 0) ==> v == 2;
   loop invariant (i > 0) ==> v == i - 2;
   loop invariant ( (i == 0 && v == 2) || (i >= 2 && v == i - 2) );
   loop invariant 0 <= i <= l;
   loop assigns v, i;
   loop variant l - i;
 */
while (i<l) {
      v = v-v;
      v = v+i;
      i = i+2;
  }

}