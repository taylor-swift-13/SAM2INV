int main1(int a,int b,int k,int q){
  int l, i, v;

  l=34;
  i=0;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i && i <= l;
    loop invariant (i == 0) ==> (v == 0);
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant q == \at(q, Pre);
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v-v;
      v = v-v;
      v = v+1;
      v = v+1;
      v = v+1;
      v = v+v;
      i = i+1;
  }

}