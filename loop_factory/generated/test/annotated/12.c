int main1(int w,int u,int v){
  int j, i, vc, pn;
  j=68;
  i=j;
  vc=5;
  pn=11;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pn - vc == 6;
  loop invariant pn - 6*i == -397;
  loop invariant i <= j;
  loop invariant i >= 68;
  loop invariant v == \at(v, Pre);
  loop invariant w == \at(w, Pre);
  loop invariant pn == 6*i - 397;
  loop invariant vc == 6*i - 403;
  loop invariant ((u + i) % 6) == (((\at(u, Pre)) + 68) % 6);
  loop assigns vc, pn, i, u;
*/
while (i<j) {
      vc += 6;
      pn += 6;
      i = i + 1;
      u = (u+pn)%6;
  }
}