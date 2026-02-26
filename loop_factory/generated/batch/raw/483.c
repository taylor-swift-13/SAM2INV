int main1(int a,int q){
  int b, c, t, v;

  b=a;
  c=b;
  t=q;
  v=-6;

  while (c>=1) {
      if (c<b/2) {
          t = t+v;
      }
      else {
          t = t+1;
      }
      t = t+3;
  }

}
