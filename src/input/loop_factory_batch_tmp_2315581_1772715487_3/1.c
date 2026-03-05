int main1(int v,int f){
  int ijj, t, nyd, o;

  ijj=v+13;
  t=ijj;
  nyd=6;
  o=0;

  while (t<=ijj-1) {
      o = t%5;
      if (t>=nyd) {
          nyd = (t-nyd)%5;
          nyd = nyd+o-nyd;
      }
      else {
          nyd = nyd + o;
      }
      t += 1;
      f += t;
  }

}
