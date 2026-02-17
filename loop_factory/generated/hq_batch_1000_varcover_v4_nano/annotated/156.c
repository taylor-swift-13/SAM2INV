int main1(int a,int k,int n){
  int l, i, v;

  l=60;
  i=0;
  v=6;

  
  /*@

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant l == 60;

    loop invariant v >= 0;

    loop invariant v == 0 || (i == 0 && v == 6);

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant n == \at(n, Pre);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v+v;
      v = v+1;
      if (i+1<=v+l) {
          v = v+1;
      }
      v = v-v;
      i = i+1;
  }

}