int main1(int b,int n,int p){
  int l, i, v;

  l=38;
  i=0;
  v=-4;

  
  /*@

    loop invariant (i == 0) ==> (v == -4);

    loop invariant i <= l;

    loop invariant 0 <= i;

    loop invariant b == \at(b, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      if ((i%2)==0) {
          v = v-v;
      }
      else {
          v = v+4;
      }
      i = i+1;
  }

}