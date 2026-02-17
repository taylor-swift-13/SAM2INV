int main1(int a,int m,int p){
  int l, i, v, c;

  l=m+14;
  i=0;
  v=a;
  c=l;

  
  /*@

    loop invariant i >= 0 && (l <= 0 || i <= l);

    loop invariant c == l + i;

    loop invariant v == \at(a,Pre) + i*(2*l + i);

    loop invariant l == \at(m,Pre) + 14;

    loop invariant a == \at(a,Pre) && m == \at(m,Pre) && p == \at(p,Pre);

    loop assigns v, c, i;

  */
while (i<l) {
      v = v+c+c;
      v = v+1;
      c = c+1;
      i = i+1;
  }

}