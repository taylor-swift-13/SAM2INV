int main1(int a,int n,int p,int q){
  int l, i, v;

  l=a+17;
  i=0;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == a + 17;
    loop invariant i >= 0;
    loop invariant (l >= 0) ==> (i <= l);
    loop invariant (i == 0) ==> (v == 4);
    loop invariant (i != 0) ==> (v == i - 1);
    loop assigns v, i;
  */
while (i<l) {
      v = v-v;
      v = v+i;
      i = i+1;
  }

}