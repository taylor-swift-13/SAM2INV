int main1(int b,int n){
  int v0, r4, jwl, t6, r2, lwl;

  v0=(n%11)+13;
  r4=0;
  jwl=9;
  t6=0;
  r2=1;
  lwl=0;

  while (1) {
      if (!(jwl>0&&r4<v0)) {
          break;
      }
      if (jwl<=r2) {
          lwl = jwl;
      }
      else {
          lwl = r2;
      }
      r4++;
      t6 = t6 + lwl;
      jwl = jwl - lwl;
      r2 += 1;
  }

}
