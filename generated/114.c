int main114(int m,int d){
  int zy4, wf, iucj;

  zy4=(d%17)+4;
  wf=0;
  iucj=m;

  while (1) {
      iucj = iucj + 3;
      wf += 1;
      if (wf>=zy4) {
          break;
      }
  }

}
