int main1(int a,int p){
  int l, i, v;

  l=14;
  i=0;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 14;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant p == \at(p, Pre);
    loop invariant a == \at(a, Pre);
    loop invariant (i == 0) ==> (v == 0);
    loop invariant (i == 0) ==> v == 0;
    loop invariant 0 <= i;
    loop invariant (i == 0 && v == 0) || (i > 0 && v == 1);
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v-v;
      v = v+1;
      i = i+1;
  }

}