int main1(int k,int n,int p){
  int l, i, v;

  l=50;
  i=l;
  v=3;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant v == 0 || (v == 3 && i == l);

    loop invariant l == 50;

    loop invariant k == \at(k, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop assigns i, v;

    loop variant i;

  */
while (i>0) {
      v = v+i;
      v = v-v;
      i = i-1;
  }

}