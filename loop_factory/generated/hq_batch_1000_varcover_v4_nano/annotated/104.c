int main1(int b,int n,int p){
  int l, i, v, x;

  l=63;
  i=l;
  v=p;
  x=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
   loop invariant i >= 0;
   loop invariant i <= l;
   loop invariant (((l - i) % 2) == 0) ==> (v == p);
   loop invariant (((l - i) % 2) != 0) ==> (v == -p - x - 1);
   loop assigns v, i;
 */
while (i>0) {
      v = v+x+x;
      v = v+1;
      v = x-v;
      i = i-1;
  }

}