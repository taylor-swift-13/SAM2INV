int main1(int b,int m,int n){
  int l, i, v;

  l=58;
  i=0;
  v=l;

  
  /*@

    loop invariant 0 <= i;

    loop invariant i <= l;

    loop invariant (i == 0 ==> v == l) && (i > 0 ==> v == 1);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop assigns v, i;

    loop variant l - i;

  */
while (i<l) {
      if (v+2<l) {
          v = v+i;
      }
      v = v-v;
      v = v+1;
      v = v;
      i = i+1;
  }

}