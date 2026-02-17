int main1(int a,int k,int m){
  int l, i, v;

  l=27;
  i=l;
  v=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v >= 1;
    loop invariant ((v + 2) % 3) == 0;
    loop assigns i, v;
    loop variant i;
  */
while (i>0) {
      v = v+1;
      v = v+v;
      i = i-1;
  }

}