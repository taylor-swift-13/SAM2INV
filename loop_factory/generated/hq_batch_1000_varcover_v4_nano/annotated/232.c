int main1(int b,int m,int p){
  int l, i, v;

  l=50;
  i=0;
  v=b;

  
  /*@

    loop invariant (i == 0 ==> v == \at(b,Pre)) && (i > 0 ==> v == 0);

    loop invariant 0 <= i && i <= l;

    loop invariant b == \at(b,Pre);

    loop invariant m == \at(m,Pre);

    loop invariant p == \at(p,Pre);

    loop assigns v, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+5;
      v = v-v;
      i = i+1;
  }

}