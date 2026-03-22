int main1(int l){
  int n, ca, gt, ocqb, df, m, n7oh, q;

  n=l+23;
  ca=-6;
  gt=1;
  ocqb=ca;
  df=0;
  m=ca;
  n7oh=ca;
  q=l;

  while (ca+1<=n) {
      if (ca%4==3) {
          gt = gt + 1;
      }
      else {
          ocqb++;
      }
      if (ca%4==0) {
          df++;
      }
      else {
      }
      m = (4)+(m);
      n7oh += 2;
      q = q + gt;
      l = (l+gt)%4;
      n = (ca+1)-1;
  }

}
