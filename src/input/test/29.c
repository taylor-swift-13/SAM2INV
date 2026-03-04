int main29(int a,int k,int q){
  int x, w, v;

  x=51;
  w=0;
  v=2;

  while (1) {
      if (v==1) {
          v = 2;
      }
      else {
          if (v==2) {
              v = 1;
          }
      }
  }

  while (x<=v-2) {
      if (w==1) {
          w = 2;
      }
      else {
          if (w==2) {
              w = 1;
          }
      }
      if (w*w<=v+6) {
          w = w*2;
      }
      else {
          w = w%7;
      }
      if (w+7<v) {
          w = w%5;
      }
  }

}
