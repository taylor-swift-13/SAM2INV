int main1(int k,int q){
  int o, l, t, s;

  o=57;
  l=0;
  t=o;
  s=k;

  while (t!=0&&s!=0) {
      if (t>s) {
          t = t-s;
      }
      else {
          s = s-t;
      }
      t = t+3;
      s = s+2;
  }

}
