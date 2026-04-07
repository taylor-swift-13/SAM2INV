int main1(int q,int i){
  int n, q5li, ev, ga, ti, wv, cq8;

  n=i+5;
  q5li=-1;
  ev=20;
  ga=n;
  ti=0;
  wv=-6;
  cq8=q5li;

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
