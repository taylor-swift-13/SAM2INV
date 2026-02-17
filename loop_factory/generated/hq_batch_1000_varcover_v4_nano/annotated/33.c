int main1(int k,int m,int n){
  int l, i, v;

  l=76;
  i=0;
  v=n;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant l == 76;

    loop invariant n == \at(n, Pre);

    loop invariant (i == 0 ==> v == \at(n, Pre));

    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      v = v+4;
      if (v+5<l) {
          v = v-v;
      }
      else {
          v = v+v;
      }
      v = v+i;
      i = i+1;
  }

}