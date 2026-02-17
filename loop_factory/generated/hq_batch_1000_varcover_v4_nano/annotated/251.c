int main1(int b,int m,int q){
  int l, i, v;

  l=q-6;
  i=0;
  v=-4;

  
  /*@

    loop invariant i >= 0;

    loop invariant (i == 0 && v == -4) || (i > 0 && v == 0);

    loop invariant (i == 0 || i <= l);

    loop invariant l == \at(q, Pre) - 6;

    loop invariant q == \at(q, Pre) && m == \at(m, Pre) && b == \at(b, Pre);

    loop assigns i, v;

  */
while (i<l) {
      v = v+1;
      v = v+3;
      v = v-v;
      i = i+1;
  }

}