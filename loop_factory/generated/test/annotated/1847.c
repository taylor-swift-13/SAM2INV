int main1(int q,int i){
  int n, q5li, ev, ga, ti, wv, cq8;
  n=i+5;
  q5li=-1;
  ev=20;
  ga=n;
  ti=0;
  wv=-6;
  cq8=q5li;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ev - ga) >= (15 - \at(i,Pre));
  loop invariant ev >= 20;
  loop invariant ga >= n;
  loop invariant i >= \at(i,Pre);
  loop invariant ti >= 0;
  loop invariant q5li == -1;
  loop invariant ((i - \at(i, Pre)) % 2) == 0;
  loop invariant wv >= -6;
  loop invariant cq8 >= -1;
  loop invariant ga - i >= 5;
  loop invariant q == \at(q, Pre);
  loop assigns ev, ga, ti, cq8, wv, i, n;
*/
while (q5li+1<=n) {
      if (ti==n+1) {
          ev = ev + 3;
          ga = ga + 3;
      }
      else {
          ev += 2;
          ga += 2;
      }
      if (!(!(ti==n))) {
          ev = ev + 1;
          ti += 1;
      }
      cq8 = cq8 + 3;
      wv += ga;
      i += 2;
      wv += 2;
      cq8 = cq8 + wv;
      n = (q5li+1)-1;
  }
}