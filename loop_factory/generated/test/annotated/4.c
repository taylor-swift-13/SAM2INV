int main1(int k,int m,int n,int p){
  int l, i, v, f;

  l=67;
  i=0;
  v=6;
  f=k;

  
  /*@

    loop invariant v == 6 + i;

    loop invariant f == \at(k, Pre) + 6*i + (i*(i+1))/2;

    loop invariant 0 <= i && i <= l;

    loop invariant k == \at(k, Pre);

    loop invariant k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop invariant i <= l;

    loop invariant f == k + 7*i + i*(i-1)/2;

    loop invariant i >= 0;

    loop invariant l == 67;

    loop invariant f == k + 6*i + i*(i+1)/2;

    loop invariant f == \at(k,Pre) + 6*i + (i*(i+1))/2;

    loop invariant k == \at(k,Pre);

    loop assigns v, f, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+1;
      f = f+v;
      i = i+1;
  }

}