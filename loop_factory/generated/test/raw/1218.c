int main1(int c,int f){
  int rk, ke, df9a, z6n, lttr;

  rk=78;
  ke=0;
  df9a=1;
  z6n=6;
  lttr=0;

  while (1) {
      if (!(lttr<=rk)) {
          break;
      }
      ke += df9a;
      lttr++;
      df9a += z6n;
      z6n += 2;
      c = c+z6n+z6n;
      f = f+(df9a%6);
  }

}
