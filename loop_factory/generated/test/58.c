int main58(int k,int p,int q){
  int r, v, o;

  r=(p%25)+15;
  v=3;
  o=v;

  while (1) {
      o = o+3;
      if (v+3<=p+r) {
          o = o*o+o;
      }
      else {
          o = o+v;
      }
  }

  while (1) {
      r = r+o;
      if (r+3<v) {
          r = r+6;
      }
      else {
          r = r+1;
      }
      o = o+1;
  }

  while (o+1<=v) {
      r = r+3;
      r = r+r;
      if (o+1<=o+v) {
          r = r+o;
      }
  }

}
