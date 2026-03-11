int main1(int p,int q){
  int s, m, u, v;

  s=p;
  m=0;
  u=s;
  v=s;


while (m+1<=s) {
      u = u*3;
      v = v/3;
      m = m+1;
  }
/*@
  assert !(m+1<=s) &&
         (p == \at(p, Pre) && q == \at(q, Pre) && s == \at(p, Pre));
*/

}
