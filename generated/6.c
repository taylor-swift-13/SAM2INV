int main6(int l,int j){
  int iw6z, ie, ah, ilq, t, xu, qh;

  iw6z=l+24;
  ie=0;
  ah=0;
  ilq=1;
  t=iw6z;
  xu=j;
  qh=j;

  while (1) {
      if (!(ilq<=iw6z)) {
          break;
      }
      if (ie%2==0) {
          ah = ah + 1;
      }
      else {
          ah--;
      }
      t = t + 3;
      ilq += 1;
      xu = xu+(ilq%5);
      qh++;
  }

}
