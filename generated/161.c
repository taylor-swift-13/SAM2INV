int main161(int i,int n){
  int v, o9g, th, o, s17, ed, k4;

  v=n+7;
  o9g=0;
  th=0;
  o=v;
  s17=v;
  ed=-6;
  k4=1;

  while (o9g<=v-1) {
      th = th + 3;
      o9g++;
      s17 = s17 + o9g;
      k4 = k4 + o9g;
      o = o + 1;
      i = i + k4;
  }

  while (1) {
      if (!(ed>=1)) {
          break;
      }
      th = th*4+5;
      o9g = o9g*th+5;
      o9g = th*th;
      i = i*i+n;
      if (ed+4<=o9g+k4) {
          n = th+ed;
      }
      ed--;
  }

}
