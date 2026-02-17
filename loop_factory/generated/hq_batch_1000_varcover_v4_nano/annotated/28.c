int main1(int k,int m,int n){
  int l, i, v;

  l=68;
  i=l;
  v=k;

  
  /*@

    loop invariant l == 68;

    loop invariant 0 <= i && i <= l;

    loop invariant k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre);

    loop invariant v == \at(k, Pre) - (l - i) * (l - 2) + ((l/2) * ((l/2) + 1) - (i/2) * ((i/2) + 1));

    loop assigns v, i;

    loop variant i;

  */
while (i>0) {
      if ((i%2)==0) {
          v = v+i;
      }
      v = v-l;
      v = v+1;
      v = v+1;
      i = i-1;
  }

}