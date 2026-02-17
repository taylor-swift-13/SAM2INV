int main1(int b,int k,int n){
  int l, i, v;

  l=(n%11)+10;
  i=0;
  v=i;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant (i == 0) ==> (v == 0);

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant n == \at(n, Pre);

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v-v;
      v = b;
      if ((i%5)==0) {
          v = v-v;
      }
      else {
          v = v+i;
      }
      v = v+i;
      i = i+1;
  }

}