int main1(int b,int k,int n){
  int l, i, v, w;

  l=77;
  i=l;
  v=6;
  w=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v + w == 6 + \at(b,Pre);
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v >= 6;
    loop invariant w <= \at(b,Pre);
    loop assigns v, w, i;
    loop variant i;
  */
while (i>0) {
      v = v+1;
      w = w-1;
      i = i/2;
  }

}