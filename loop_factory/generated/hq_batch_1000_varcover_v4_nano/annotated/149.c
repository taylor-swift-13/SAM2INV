int main1(int a,int b,int m){
  int l, i, v;

  l=40;
  i=0;
  v=-2;

  
  /*@

    loop invariant l == 40;

    loop invariant 0 <= i <= l;

    loop invariant (i == 0) ==> (v == -2);

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      v = v-v;
      v = v+v;
      v = v+v;
      v = v+6;
      i = i+1;
  }

}