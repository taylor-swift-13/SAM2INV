int main65(int n,int o,int w){
  int o4c, rxh;

  o4c=n;
  rxh=w;

  while (o4c!=0&&rxh!=0) {
      if (o4c>rxh) {
          o4c -= rxh;
      }
      else {
          rxh -= o4c;
      }
      n += 2;
      o = o+o4c-rxh;
      n += 1;
  }

}
