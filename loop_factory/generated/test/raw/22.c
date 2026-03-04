int main1(){
  int x7u, ql, shfl;

  x7u=1;
  ql=x7u;
  shfl=ql;

  while (1) {
      if (!(ql<x7u)) {
          break;
      }
      shfl = shfl + 3;
      ql += 1;
      shfl = shfl + shfl;
  }

}
