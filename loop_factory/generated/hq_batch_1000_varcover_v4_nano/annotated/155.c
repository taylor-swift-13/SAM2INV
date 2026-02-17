int main1(int b,int k,int m){
  int l, i, v;

  l=71;
  i=l;
  v=m;

  
  /*@

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant 0 <= i <= l;

    loop invariant v == m + (l - i);

    loop assigns v, i;

  */
  while (i>0) {
      if (b<b+1) {
          v = v+1;
      }
      else {
          v = v+1;
      }
      i = i-1;
  }

}