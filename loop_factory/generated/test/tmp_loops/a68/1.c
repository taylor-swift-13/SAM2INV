int main1(int n,int x){
  int b70r, fk, g4, f8, wfk, j4, s35, erf;

  b70r=n;
  fk=0;
  g4=(n%20)+10;
  f8=(n%15)+8;
  wfk=20;
  j4=b70r;
  s35=0;
  erf=-5;

  while (g4>0&&f8>0) {
      if (fk%2==0) {
          g4 = g4 - 1;
      }
      else {
          f8 = f8 - 1;
      }
      fk += 1;
      if (wfk+7<b70r) {
          wfk = erf*erf;
      }
      wfk = wfk*3;
      j4 = j4+(fk%2);
      x += f8;
      erf += 1;
      s35 = s35*2;
      j4 = j4/3;
  }

}
