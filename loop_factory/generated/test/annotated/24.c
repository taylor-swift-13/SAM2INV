int main1(int a,int k,int m,int p){
  int l, i, v, u, t;

  l=20;
  i=1;
  v=-1;
  u=a;
  t=m;


/*@

  loop invariant a == \at(a, Pre);

  loop invariant k == \at(k, Pre);

  loop invariant m == \at(m, Pre);

  loop invariant p == \at(p, Pre);

  loop invariant u == a;

  loop invariant t == m;

  loop invariant l == 20;

  loop invariant i >= 1;


  loop invariant i <= 2 * l;


  loop invariant (i == 1) ==> (v == -1);

  loop assigns v, i;

  loop variant l - i;

*/
while (i<l) {
      v = v+u+t;
      v = v+1;
      i = i*2;
  }

}